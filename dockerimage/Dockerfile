#!/usr/bin/env -S docker build . --tag=obelisk/AIsandbox:v1 --network=host --file


# syntax=docker/dockerfile:1

# Build an image with the Python 3.12 image
FROM python:3.12-alpine

# Set the working directory to `/code`
WORKDIR /code

# Set environment variables used by the `flask` command
# ENV FLASK_APP=app.py
# ENV FLASK_RUN_HOST=0.0.0.0

#
RUN apk update

# Install `gcc` and other dependencies
RUN apk add --no-cache gcc musl-dev linux-headers

#
RUN apk add openssh

# Copy `requirements.txt`
COPY requirements.txt .

# Install the Python dependencies
RUN pip install -r requirements.txt

# Copy the current directory `.` in the project to the workdir `.` in the image
COPY . .

EXPOSE 5000

# Set the default command for the container to `flask run --debug`
# CMD ["flask", "run", "--debug"]
CMD "bash"

